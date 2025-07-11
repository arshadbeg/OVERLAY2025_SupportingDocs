import csv
import re
import time
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.service import Service

def extract_test_cases(url, driver_path, output_csv):
    # Set up Selenium WebDriver
    service = Service(driver_path)
    options = webdriver.ChromeOptions()
    options.add_argument('--headless')  # Run in headless mode
    driver = webdriver.Chrome(service=service, options=options)

    try:
        driver.get(url)
        time.sleep(5)  # Wait for the page to load

        # Locate all test case tabs
        tab_elements = driver.find_elements(By.CSS_SELECTOR, '.tab')
        test_data = []
        input_var_names = set()

        for index, tab in enumerate(tab_elements):
            try:
                tab.click()
                time.sleep(2)  # Wait for content to load

                # Extract content from the active tab
                content_element = driver.find_element(By.CSS_SELECTOR, '.tab-content.active')
                content = content_element.text

                # Extract path
                path_match = re.search(r'Path\s*\n(.+)', content)
                path = path_match.group(1).strip() if path_match else ''

                # Extract inputs dynamically (e.g., a = 1, b = -2.5, etc.)
                inputs = dict(re.findall(r'([a-zA-Z_][a-zA-Z_0-9]*)\s*=\s*([-\d\.]+)', content))
                input_var_names.update(inputs.keys())

                # Extract return value
                return_value_match = re.search(r'return value\s+(\d+)', content)
                return_value = return_value_match.group(1) if return_value_match else ''

                # Extract verdict
                verdict_match = re.search(r'Verdict\s*\n(.+)', content)
                verdict = verdict_match.group(1).strip() if verdict_match else ''

                # Extract path predicate
                predicate_match = re.search(r'Path predicate\n(.+?)(?:\n\n|\Z)', content, re.DOTALL)
                path_predicate = predicate_match.group(1).strip().replace('\n', ' ') if predicate_match else ''

                test_case = {
                    'Test Case': index + 1,
                    'Path': path,
                    'Return Value': return_value,
                    'Verdict': verdict,
                    'Path Predicate': path_predicate
                }
                test_case.update(inputs)  # Add dynamic inputs
                test_data.append(test_case)

            except Exception as e:
                print(f"Error processing tab {index + 1}: {e}")
                continue

        # Prepare headers
        base_headers = ['Test Case', 'Path', 'Return Value', 'Verdict', 'Path Predicate']
        input_headers = sorted(input_var_names)
        all_headers = base_headers[:2] + input_headers + base_headers[2:]

        # Write to CSV
        with open(output_csv, 'w', newline='') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=all_headers)
            writer.writeheader()
            for row in test_data:
                writer.writerow({header: row.get(header, '') for header in all_headers})

        print(f"Data extraction complete. Results saved to {output_csv}")

    finally:
        driver.quit()

# Example usage
if __name__ == "__main__":
    url = "http://pathcrawler-online.com:8080/doSendExample"
    driver_path = "/usr/bin/chromedriver"
    output_csv = "pathcrawler_results.csv"
    extract_test_cases(url, driver_path, output_csv)
